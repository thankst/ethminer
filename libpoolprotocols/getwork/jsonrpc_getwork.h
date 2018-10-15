/**
 * This file is generated by jsonrpcstub, DO NOT CHANGE IT MANUALLY!
 */

#ifndef JSONRPC_CPP_STUB_GETWORK_H_
#define JSONRPC_CPP_STUB_GETWORK_H_

#include <jsonrpccpp/client.h>

class JsonrpcGetwork
{
    public:
        JsonrpcGetwork(jsonrpc::IClientConnector* conn) {
			this->client = new jsonrpc::Client(*conn);
		}

        Json::Value eth_getWork()
        {
            Json::Value p;
            p = Json::nullValue;
            Json::Value result = this->client->CallMethod("etrue_getWork",p);
            if (result.isArray())
                return result;
            else
                throw jsonrpc::JsonRpcException(jsonrpc::Errors::ERROR_CLIENT_INVALID_RESPONSE, result.toStyledString());
        }
        bool eth_submitWork(const std::string& param1, const std::string& param2, const std::string& param3)
        {
            Json::Value p;
            p.append(param1);
            p.append(param2);
            p.append(param3);
            Json::Value result = this->client->CallMethod("etrue_submitWork",p);
            if (result.isBool())
                return result.asBool();
            else
                throw jsonrpc::JsonRpcException(jsonrpc::Errors::ERROR_CLIENT_INVALID_RESPONSE, result.toStyledString());
        }
        bool eth_submitHashrate(const std::string& param1, const std::string& param2)
        {
            Json::Value p;
            p.append(param1);
            p.append(param2);
            Json::Value result = this->client->CallMethod("etrue_submitHashrate",p);
            if (result.isBool())
                return result.asBool();
            else
                throw jsonrpc::JsonRpcException(jsonrpc::Errors::ERROR_CLIENT_INVALID_RESPONSE, result.toStyledString());
        }
private:
	jsonrpc::Client* client;
};

#endif //JSONRPC_CPP_STUB_GETWORK_H_
